export const SITE = {
  website: "https://andreyyao.github.io/", // replace this with your deployed domain
  author: "Andrey Yao",
  profile: "https://andreyyao.github.io/",
  desc: "Andrey's personal website",
  title: "Andrey Yao",
  ogImage: "astropaper-og.jpg",
  lightAndDarkMode: false,
  postPerIndex: 4,
  postPerPage: 4,
  scheduledPostMargin: 15 * 60 * 1000, // 15 minutes
  showBackButton: true, // show back button in post detail
  dynamicOgImage: true,
  dir: "ltr", // "rtl" | "auto"
  lang: "en", // html lang code. Set this empty and default will be "en"
  timezone: "America/Chicago", // Default global timezone (IANA format) https://en.wikipedia.org/wiki/List_of_tz_database_time_zones
} as const;
